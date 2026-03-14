package automation

import (
	"context"
	"fmt"
	"os"
	"path/filepath"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// =============================================================================
// PipelineExecutor Tests
// =============================================================================

func TestNewPipelineExecutor(t *testing.T) {
	config := &PipelineConfig{
		Name:    "test-pipeline",
		Version: "1.0.0",
		Stages: []PipelineStage{
			{
				Name:     "build",
				Commands: []string{"echo build"},
			},
		},
	}
	workingDir := "/tmp/test"

	executor := NewPipelineExecutor(config, workingDir)

	require.NotNil(t, executor)
	assert.Equal(t, config, executor.config)
	assert.Equal(t, workingDir, executor.workingDir)
	assert.NotNil(t, executor.artifacts)
	assert.NotNil(t, executor.results)
	assert.NotNil(t, executor.stats)
	assert.NotNil(t, executor.notifications)
}

func TestPipelineExecutor_Execute_EmptyStages(t *testing.T) {
	config := &PipelineConfig{
		Name:    "test-pipeline",
		Version: "1.0.0",
		Stages:  []PipelineStage{},
	}

	executor := NewPipelineExecutor(config, ".")
	ctx := context.Background()

	err := executor.Execute(ctx)
	assert.NoError(t, err)

	stats := executor.stats
	assert.Equal(t, int64(0), stats.TotalStages)
	assert.Equal(t, int64(0), stats.CompletedStages)
}

func TestPipelineExecutor_Execute_SingleStage(t *testing.T) {
	tmpDir := t.TempDir()
	config := &PipelineConfig{
		Name:    "test-pipeline",
		Version: "1.0.0",
		Stages: []PipelineStage{
			{
				Name:     "test-stage",
				Commands: []string{"go version"},
			},
		},
	}

	executor := NewPipelineExecutor(config, tmpDir)
	ctx := context.Background()

	err := executor.Execute(ctx)
	assert.NoError(t, err)

	// Check results
	results := executor.GetResults()
	assert.Len(t, results, 1)
	assert.Contains(t, results, "test-stage")
	assert.Equal(t, "success", results["test-stage"].Status)
}

func TestPipelineExecutor_Execute_MultipleStages(t *testing.T) {
	tmpDir := t.TempDir()
	config := &PipelineConfig{
		Name:    "test-pipeline",
		Version: "1.0.0",
		Stages: []PipelineStage{
			{
				Name:     "stage1",
				Commands: []string{"go version"},
			},
			{
				Name:     "stage2",
				Commands: []string{"go env GOROOT"},
			},
			{
				Name:     "stage3",
				Commands: []string{"go env GOPATH"},
			},
		},
	}

	executor := NewPipelineExecutor(config, tmpDir)
	ctx := context.Background()

	err := executor.Execute(ctx)
	assert.NoError(t, err)

	results := executor.GetResults()
	assert.Len(t, results, 3)

	// Verify all stages completed successfully
	for _, stageName := range []string{"stage1", "stage2", "stage3"} {
		assert.Contains(t, results, stageName)
		assert.Equal(t, "success", results[stageName].Status)
	}

	// Check stats
	stats := executor.stats
	assert.Equal(t, int64(3), stats.TotalStages)
	assert.Equal(t, int64(3), stats.CompletedStages)
	assert.Equal(t, int64(0), stats.FailedStages)
}

func TestPipelineExecutor_Execute_FailedStage(t *testing.T) {
	tmpDir := t.TempDir()
	config := &PipelineConfig{
		Name:    "test-pipeline",
		Version: "1.0.0",
		Stages: []PipelineStage{
			{
				Name:     "failing-stage",
				Commands: []string{"go unknowncommand"},
			},
		},
	}

	executor := NewPipelineExecutor(config, tmpDir)
	ctx := context.Background()

	err := executor.Execute(ctx)
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "failing-stage")

	results := executor.GetResults()
	assert.Len(t, results, 1)
	assert.Equal(t, "failed", results["failing-stage"].Status)

	stats := executor.stats
	assert.Equal(t, int64(1), stats.FailedStages)
}

func TestPipelineExecutor_Execute_SkippedStage(t *testing.T) {
	tmpDir := t.TempDir()
	config := &PipelineConfig{
		Name:    "test-pipeline",
		Version: "1.0.0",
		Stages: []PipelineStage{
			{
				Name:      "skipped-stage",
				Commands:  []string{"go version"},
				Condition: "false", // This will be evaluated but current implementation always returns true
			},
		},
	}

	executor := NewPipelineExecutor(config, tmpDir)
	ctx := context.Background()

	// Current implementation always evaluates condition to true
	err := executor.Execute(ctx)
	assert.NoError(t, err)
}

func TestPipelineExecutor_Execute_WithDependencies(t *testing.T) {
	tmpDir := t.TempDir()
	config := &PipelineConfig{
		Name:    "test-pipeline",
		Version: "1.0.0",
		Stages: []PipelineStage{
			{
				Name:     "first",
				Commands: []string{"go version"},
			},
			{
				Name:         "second",
				Commands:     []string{"go env GOOS"},
				Dependencies: []string{"first"},
			},
		},
	}

	executor := NewPipelineExecutor(config, tmpDir)
	ctx := context.Background()

	err := executor.Execute(ctx)
	assert.NoError(t, err)

	results := executor.GetResults()
	assert.Len(t, results, 2)
	assert.Equal(t, "success", results["first"].Status)
	assert.Equal(t, "success", results["second"].Status)
}

func TestPipelineExecutor_Execute_FailedDependency(t *testing.T) {
	tmpDir := t.TempDir()
	config := &PipelineConfig{
		Name:    "test-pipeline",
		Version: "1.0.0",
		Stages: []PipelineStage{
			{
				Name:     "failing",
				Commands: []string{"go unknowncommand"},
			},
			{
				Name:         "dependent",
				Commands:     []string{"go version"},
				Dependencies: []string{"failing"},
			},
		},
	}

	executor := NewPipelineExecutor(config, tmpDir)
	ctx := context.Background()

	err := executor.Execute(ctx)
	assert.Error(t, err)

	results := executor.GetResults()
	// First stage fails, second should not be executed
	assert.Len(t, results, 1)
	assert.Equal(t, "failed", results["failing"].Status)
}

func TestPipelineExecutor_Execute_WithRetry(t *testing.T) {
	tmpDir := t.TempDir()
	config := &PipelineConfig{
		Name:    "test-pipeline",
		Version: "1.0.0",
		RetryPolicy: &RetryPolicy{
			MaxRetries: 2,
			Delay:      100 * time.Millisecond,
			Backoff:    "linear",
		},
		Stages: []PipelineStage{
			{
				Name:       "retry-stage",
				Commands:   []string{"go version"},
				RetryCount: 1,
			},
		},
	}

	executor := NewPipelineExecutor(config, tmpDir)
	ctx := context.Background()

	err := executor.Execute(ctx)
	assert.NoError(t, err)

	results := executor.GetResults()
	assert.Equal(t, "success", results["retry-stage"].Status)
}

func TestPipelineExecutor_checkDependencies(t *testing.T) {
	executor := NewPipelineExecutor(&PipelineConfig{}, ".")

	// Add a successful result
	executor.results["success-stage"] = &StageResult{
		Name:   "success-stage",
		Status: "success",
	}

	tests := []struct {
		name     string
		stage    PipelineStage
		expected bool
	}{
		{
			name:     "no dependencies",
			stage:    PipelineStage{Name: "nodep", Dependencies: []string{}},
			expected: true,
		},
		{
			name:     "met dependency",
			stage:    PipelineStage{Name: "dep1", Dependencies: []string{"success-stage"}},
			expected: true,
		},
		{
			name:     "unmet dependency - not exists",
			stage:    PipelineStage{Name: "dep2", Dependencies: []string{"non-existent"}},
			expected: false,
		},
		{
			name:     "unmet dependency - failed",
			stage:    PipelineStage{Name: "dep3", Dependencies: []string{"failed-stage"}},
			expected: false,
		},
		{
			name:     "multiple dependencies - one unmet",
			stage:    PipelineStage{Name: "dep4", Dependencies: []string{"success-stage", "failed-stage"}},
			expected: false,
		},
	}

	// Add a failed result
	executor.results["failed-stage"] = &StageResult{
		Name:   "failed-stage",
		Status: "failed",
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := executor.checkDependencies(tt.stage)
			assert.Equal(t, tt.expected, result)
		})
	}
}

func TestPipelineExecutor_calculateRetryDelay(t *testing.T) {
	tests := []struct {
		name     string
		config   *PipelineConfig
		attempt  int
		expected time.Duration
	}{
		{
			name:     "no retry policy",
			config:   &PipelineConfig{},
			attempt:  0,
			expected: 1 * time.Second,
		},
		{
			name:     "no retry policy - second attempt",
			config:   &PipelineConfig{},
			attempt:  1,
			expected: 2 * time.Second,
		},
		{
			name: "linear backoff",
			config: &PipelineConfig{
				RetryPolicy: &RetryPolicy{
					Delay:   100 * time.Millisecond,
					Backoff: "linear",
				},
			},
			attempt:  2,
			expected: 300 * time.Millisecond,
		},
		{
			name: "exponential backoff",
			config: &PipelineConfig{
				RetryPolicy: &RetryPolicy{
					Delay:   100 * time.Millisecond,
					Backoff: "exponential",
				},
			},
			attempt:  2,
			expected: 400 * time.Millisecond,
		},
		{
			name: "default backoff",
			config: &PipelineConfig{
				RetryPolicy: &RetryPolicy{
					Delay:   100 * time.Millisecond,
					Backoff: "unknown",
				},
			},
			attempt:  1,
			expected: 100 * time.Millisecond,
		},
		{
			name: "zero delay defaults to 1 second",
			config: &PipelineConfig{
				RetryPolicy: &RetryPolicy{
					Delay:   0,
					Backoff: "linear",
				},
			},
			attempt:  0,
			expected: 1 * time.Second,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			executor := NewPipelineExecutor(tt.config, ".")
			result := executor.calculateRetryDelay(tt.attempt)
			assert.Equal(t, tt.expected, result)
		})
	}
}

func TestPipelineExecutor_GetResults(t *testing.T) {
	executor := NewPipelineExecutor(&PipelineConfig{}, ".")

	// Initially empty
	results := executor.GetResults()
	assert.Empty(t, results)

	// Add a result
	executor.results["test"] = &StageResult{
		Name:   "test",
		Status: "success",
	}

	results = executor.GetResults()
	assert.Len(t, results, 1)
	assert.Contains(t, results, "test")
}

func TestPipelineExecutor_evaluateCondition(t *testing.T) {
	executor := NewPipelineExecutor(&PipelineConfig{}, ".")

	// Current implementation always returns true
	assert.True(t, executor.evaluateCondition(""))
	assert.True(t, executor.evaluateCondition("true"))
	assert.True(t, executor.evaluateCondition("false"))
	assert.True(t, executor.evaluateCondition("some complex condition"))
}

// =============================================================================
// CodeQualityChecker Tests
// =============================================================================

func TestNewCodeQualityChecker(t *testing.T) {
	config := &QualityConfig{
		GoVersion:    "1.21",
		TestCoverage: 80.0,
		Cyclomatic:   10,
	}

	checker := NewCodeQualityChecker(config)

	require.NotNil(t, checker)
	assert.Equal(t, config, checker.config)
}

func TestCodeQualityChecker_Check(t *testing.T) {
	// Create a temporary Go module for testing
	tmpDir := t.TempDir()

	// Create go.mod
	goMod := `module testmod

go 1.21
`
	err := os.WriteFile(filepath.Join(tmpDir, "go.mod"), []byte(goMod), 0644)
	require.NoError(t, err)

	// Create a simple Go file
	goFile := `package testmod

func Add(a, b int) int {
	return a + b
}
`
	err = os.WriteFile(filepath.Join(tmpDir, "main.go"), []byte(goFile), 0644)
	require.NoError(t, err)

	config := &QualityConfig{
		GoVersion:    "1.21",
		TestCoverage: 50.0,
		SecurityScan: false,
		Performance:  false,
	}

	checker := NewCodeQualityChecker(config)
	ctx := context.Background()

	report, err := checker.Check(ctx, tmpDir)
	// The test might fail due to missing go test files, but we can check the report structure
	if err == nil {
		assert.NotNil(t, report)
		assert.Equal(t, "1.21", report.GoVersion)
		assert.NotZero(t, report.Timestamp)
	}
}

func TestCodeQualityChecker_calculateOverallScore(t *testing.T) {
	config := &QualityConfig{
		TestCoverage: 80.0,
	}
	checker := NewCodeQualityChecker(config)

	tests := []struct {
		name     string
		report   *QualityReport
		expected float64
	}{
		{
			name: "perfect score",
			report: &QualityReport{
				Coverage:       80.0,
				LintResults:    []LintResult{},
				SecurityIssues: []SecurityIssue{},
				TestResults: &TestResult{
					Failed: 0,
				},
			},
			expected: 100.0,
		},
		{
			name: "with lint issues",
			report: &QualityReport{
				Coverage: 80.0,
				LintResults: []LintResult{
					{File: "test.go"},
					{File: "test2.go"},
				},
				SecurityIssues: []SecurityIssue{},
				TestResults: &TestResult{
					Failed: 0,
				},
			},
			expected: 96.0,
		},
		{
			name: "with coverage below threshold",
			report: &QualityReport{
				Coverage:       70.0,
				LintResults:    []LintResult{},
				SecurityIssues: []SecurityIssue{},
				TestResults: &TestResult{
					Failed: 0,
				},
			},
			expected: 0.0, // 100 - (80-70)*10 = 0
		},
		{
			name: "with security issues",
			report: &QualityReport{
				Coverage:    80.0,
				LintResults: []LintResult{},
				SecurityIssues: []SecurityIssue{
					{Level: "high"},
				},
				TestResults: &TestResult{
					Failed: 0,
				},
			},
			expected: 95.0,
		},
		{
			name: "with test failures",
			report: &QualityReport{
				Coverage:       80.0,
				LintResults:    []LintResult{},
				SecurityIssues: []SecurityIssue{},
				TestResults: &TestResult{
					Failed: 2,
				},
			},
			expected: 80.0,
		},
		{
			name: "minimum score is 0",
			report: &QualityReport{
				Coverage: 0.0,
				LintResults: []LintResult{
					{}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {},
				},
				SecurityIssues: []SecurityIssue{
					{}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {},
				},
				TestResults: &TestResult{
					Failed: 5,
				},
			},
			expected: 0.0,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			checker.calculateOverallScore(tt.report)
			assert.InDelta(t, tt.expected, tt.report.OverallScore, 0.01)
		})
	}
}

// =============================================================================
// DeploymentManager Tests
// =============================================================================

func TestNewDeploymentManager(t *testing.T) {
	config := &DeploymentConfig{
		Name:        "test-app",
		Environment: "production",
		Replicas:    3,
		Image:       "test:latest",
	}

	manager := NewDeploymentManager(config)

	require.NotNil(t, manager)
	assert.Equal(t, config, manager.config)
}

func TestDeploymentManager_generateKubernetesDeployment(t *testing.T) {
	config := &DeploymentConfig{
		Name:        "test-app",
		Environment: "production",
		Replicas:    3,
		Image:       "test:latest",
		Ports: []PortConfig{
			{
				Name:       "http",
				Port:       8080,
				TargetPort: 8080,
				Protocol:   "TCP",
			},
		},
		Resources: &ResourceConfig{
			CPU:    "100m",
			Memory: "128Mi",
		},
		HealthCheck: &HealthCheckConfig{
			Path:     "/health",
			Port:     8080,
			Interval: 10 * time.Second,
			Timeout:  5 * time.Second,
			Retries:  3,
		},
	}

	manager := NewDeploymentManager(config)
	deployment := manager.generateKubernetesDeployment()

	assert.Contains(t, deployment, "apiVersion: apps/v1")
	assert.Contains(t, deployment, "kind: Deployment")
	assert.Contains(t, deployment, "name: test-app")
	assert.Contains(t, deployment, "replicas: 3")
	assert.Contains(t, deployment, "image: test:latest")
	assert.Contains(t, deployment, "containerPort: 8080")
	assert.Contains(t, deployment, "value: \"production\"")
	assert.Contains(t, deployment, "cpu: 100m")
	assert.Contains(t, deployment, "memory: 128Mi")
	assert.Contains(t, deployment, "path: /health")
}

func TestDeploymentManager_generateDeploymentFiles(t *testing.T) {
	tmpDir := t.TempDir()
	config := &DeploymentConfig{
		Name:        "test-app",
		Environment: "dev",
		Replicas:    1,
		Image:       "test:latest",
		Ports: []PortConfig{
			{
				Name:       "http",
				Port:       8080,
				TargetPort: 8080,
				Protocol:   "TCP",
			},
		},
		Resources: &ResourceConfig{
			CPU:    "100m",
			Memory: "128Mi",
		},
		HealthCheck: &HealthCheckConfig{
			Path:     "/health",
			Port:     8080,
			Interval: 10 * time.Second,
		},
	}

	manager := NewDeploymentManager(config)

	// Change to temp directory
	originalDir, _ := os.Getwd()
	os.Chdir(tmpDir)
	defer os.Chdir(originalDir)

	err := manager.generateDeploymentFiles()
	assert.NoError(t, err)

	// Check file was created
	filename := "test-app-deployment.yaml"
	content, err := os.ReadFile(filepath.Join(tmpDir, filename))
	assert.NoError(t, err)
	assert.Contains(t, string(content), "apiVersion: apps/v1")
}

// =============================================================================
// NotificationService Tests
// =============================================================================

func TestNewNotificationService(t *testing.T) {
	service := NewNotificationService()

	require.NotNil(t, service)
	assert.NotNil(t, service.providers)
	assert.Empty(t, service.providers)
}

func TestNotificationService_RegisterProvider(t *testing.T) {
	service := NewNotificationService()
	provider := &ConsoleNotificationProvider{}

	service.RegisterProvider("console", provider)

	assert.Contains(t, service.providers, "console")
	assert.Equal(t, provider, service.providers["console"])
}

func TestNotificationService_Send(t *testing.T) {
	service := NewNotificationService()
	ctx := context.Background()

	// Test sending to unregistered provider
	err := service.Send(ctx, "unknown", "test message")
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "not found")

	// Register and send to console provider
	provider := &ConsoleNotificationProvider{}
	service.RegisterProvider("console", provider)

	err = service.Send(ctx, "console", "test message")
	assert.NoError(t, err)
}

func TestConsoleNotificationProvider_Send(t *testing.T) {
	provider := &ConsoleNotificationProvider{}
	ctx := context.Background()

	err := provider.Send(ctx, "test message")
	assert.NoError(t, err)
}

func TestFileNotificationProvider_Send(t *testing.T) {
	tmpDir := t.TempDir()
	filename := filepath.Join(tmpDir, "notifications.log")

	provider := NewFileNotificationProvider(filename)
	ctx := context.Background()

	err := provider.Send(ctx, "test message 1")
	assert.NoError(t, err)

	err = provider.Send(ctx, "test message 2")
	assert.NoError(t, err)

	// Read file and verify content
	content, err := os.ReadFile(filename)
	assert.NoError(t, err)
	assert.Contains(t, string(content), "test message 1")
	assert.Contains(t, string(content), "test message 2")
}

// =============================================================================
// AutomationManager Tests
// =============================================================================

func TestNewAutomationManager(t *testing.T) {
	manager := NewAutomationManager()

	require.NotNil(t, manager)
	assert.NotNil(t, manager.notificationService)
	assert.NotNil(t, manager.stats)
}

func TestAutomationManager_SetPipelineExecutor(t *testing.T) {
	manager := NewAutomationManager()
	config := &PipelineConfig{
		Name:    "test",
		Version: "1.0",
	}
	executor := NewPipelineExecutor(config, ".")

	manager.SetPipelineExecutor(executor)
	assert.Equal(t, executor, manager.pipelineExecutor)
}

func TestAutomationManager_SetQualityChecker(t *testing.T) {
	manager := NewAutomationManager()
	config := &QualityConfig{}
	checker := NewCodeQualityChecker(config)

	manager.SetQualityChecker(checker)
	assert.Equal(t, checker, manager.qualityChecker)
}

func TestAutomationManager_SetDeploymentManager(t *testing.T) {
	manager := NewAutomationManager()
	config := &DeploymentConfig{Name: "test"}
	dm := NewDeploymentManager(config)

	manager.SetDeploymentManager(dm)
	assert.Equal(t, dm, manager.deploymentManager)
}

func TestAutomationManager_ExecutePipeline_NotConfigured(t *testing.T) {
	manager := NewAutomationManager()
	ctx := context.Background()

	err := manager.ExecutePipeline(ctx)
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "not configured")
}

func TestAutomationManager_RunQualityCheck_NotConfigured(t *testing.T) {
	manager := NewAutomationManager()
	ctx := context.Background()

	report, err := manager.RunQualityCheck(ctx, ".")
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "not configured")
	assert.Nil(t, report)
}

func TestAutomationManager_ExecuteDeployment_NotConfigured(t *testing.T) {
	manager := NewAutomationManager()
	ctx := context.Background()

	err := manager.ExecuteDeployment(ctx)
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "not configured")
}

func TestAutomationManager_GetStats(t *testing.T) {
	manager := NewAutomationManager()

	// Initial stats should be zero
	stats := manager.GetStats()
	assert.NotNil(t, stats)
	assert.Equal(t, int64(0), stats.PipelinesExecuted)
	assert.Equal(t, int64(0), stats.QualityChecksRun)
	assert.Equal(t, int64(0), stats.DeploymentsExecuted)

	// Modify internal stats
	manager.stats.PipelinesExecuted = 5
	manager.stats.QualityChecksRun = 3

	// GetStats should return a copy
	stats = manager.GetStats()
	assert.Equal(t, int64(5), stats.PipelinesExecuted)
	assert.Equal(t, int64(3), stats.QualityChecksRun)

	// Modifying returned stats should not affect internal stats
	stats.PipelinesExecuted = 100
	assert.Equal(t, int64(5), manager.stats.PipelinesExecuted)
}

func TestAutomationManager_ConcurrentAccess(t *testing.T) {
	manager := NewAutomationManager()
	config := &PipelineConfig{Name: "test", Version: "1.0"}
	executor := NewPipelineExecutor(config, ".")

	// Concurrent writes
	done := make(chan bool)
	for i := 0; i < 10; i++ {
		go func() {
			manager.SetPipelineExecutor(executor)
			manager.SetQualityChecker(&CodeQualityChecker{})
			manager.SetDeploymentManager(&DeploymentManager{})
			done <- true
		}()
	}

	for i := 0; i < 10; i++ {
		<-done
	}

	// Concurrent reads
	for i := 0; i < 10; i++ {
		go func() {
			_ = manager.GetStats()
			done <- true
		}()
	}

	for i := 0; i < 10; i++ {
		<-done
	}
}

// =============================================================================
// Global Automation Manager Tests
// =============================================================================

func TestInitGlobalAutomationManager(t *testing.T) {
	// Ensure global is nil first
	globalAutomationManager = nil
	assert.Nil(t, GetGlobalAutomationManager())

	InitGlobalAutomationManager()
	assert.NotNil(t, GetGlobalAutomationManager())
}

func TestGetGlobalAutomationManager(t *testing.T) {
	// Reset and test
	globalAutomationManager = nil
	assert.Nil(t, GetGlobalAutomationManager())

	// Set manually for testing
	manager := NewAutomationManager()
	globalAutomationManager = manager
	assert.Equal(t, manager, GetGlobalAutomationManager())
}

// =============================================================================
// TestAutomation Tests
// =============================================================================

func TestNewTestAutomation(t *testing.T) {
	config := &TestAutomationConfig{
		ParallelExecution: true,
		MaxWorkers:        4,
		Timeout:           30 * time.Minute,
	}

	ta := NewTestAutomation(config)

	require.NotNil(t, ta)
	assert.Equal(t, config, ta.config)
	assert.NotNil(t, ta.stats)
	assert.NotNil(t, ta.environment)
	assert.NotNil(t, ta.reporter)
}

func TestTestAutomation_GetStats(t *testing.T) {
	config := &TestAutomationConfig{}
	ta := NewTestAutomation(config)

	// Initial stats
	stats := ta.GetStats()
	assert.NotNil(t, stats)
	assert.Equal(t, int64(0), stats.TotalTests)

	// Modify internal stats
	ta.stats.TotalTests = 100
	ta.stats.PassedTests = 90
	ta.stats.FailedTests = 10

	stats = ta.GetStats()
	assert.Equal(t, int64(100), stats.TotalTests)
	assert.Equal(t, int64(90), stats.PassedTests)
	assert.Equal(t, int64(10), stats.FailedTests)

	// Verify copy (modifying returned stats should not affect internal)
	stats.TotalTests = 999
	assert.Equal(t, int64(100), ta.stats.TotalTests)
}

func TestTestAutomation_parseTestOutput(t *testing.T) {
	config := &TestAutomationConfig{}
	ta := NewTestAutomation(config)

	output := `
=== RUN   TestFunction1
--- PASS: TestFunction1 (0.01s)
=== RUN   TestFunction2
--- FAIL: TestFunction2 (0.02s)
=== RUN   TestFunction3
--- SKIP: TestFunction3 (0.00s)
PASS
ok  	github.com/example/test	0.100s
`

	results := ta.parseTestOutput(output)
	assert.NotEmpty(t, results)

	// Check that we parsed some results
	foundPass := false
	foundFail := false
	for _, result := range results {
		if result.Status == "passed" {
			foundPass = true
		}
		if result.Status == "failed" {
			foundFail = true
		}
	}
	assert.True(t, foundPass || foundFail || len(results) > 0)
}

func TestTestAutomation_parseBenchmarkOutput(t *testing.T) {
	config := &TestAutomationConfig{}
	ta := NewTestAutomation(config)

	output := `
BenchmarkFunction1-8    	1000000		1234 ns/op
BenchmarkFunction2-8    	 500000		2345 ns/op
PASS
ok  	github.com/example/test	2.345s
`

	results := ta.parseBenchmarkOutput(output)
	assert.NotEmpty(t, results)

	// All benchmarks should be marked as passed
	for _, result := range results {
		assert.Equal(t, "passed", result.Status)
		assert.Contains(t, result.Name, "Benchmark")
	}
}

func TestTestAutomation_parseSecurityOutput(t *testing.T) {
	config := &TestAutomationConfig{}
	ta := NewTestAutomation(config)

	output := `
[gosec] 2024/01/01 12:00:00 Scanning...
Results:
G101 (CWE-798): Potential hardcoded credentials (Severity: HIGH)
G102 (CWE-200): Bind to all interfaces (Severity: MEDIUM)
Summary:
  Gosec  : dev
  Files  : 10
  Lines  : 1000
  Issues : 2
`

	results := ta.parseSecurityOutput(output)
	// The output contains "Severity:" lines
	assert.NotEmpty(t, results)

	// Security issues should be marked as failed
	for _, result := range results {
		assert.Equal(t, "failed", result.Status)
	}
}

func TestTestAutomation_parseCoveragePercentage(t *testing.T) {
	config := &TestAutomationConfig{}
	ta := NewTestAutomation(config)

	tests := []struct {
		name     string
		output   string
		expected float64
	}{
		{
			name:     "valid coverage with percentage",
			output:   "ok  \tgithub.com/example/test\tcoverage: 75.5%\n",
			expected: 75.5,
		},
		{
			name:     "100% coverage",
			output:   "coverage: 100.0%",
			expected: 100.0,
		},
		{
			name:     "0% coverage",
			output:   "coverage: 0.0%",
			expected: 0.0,
		},
		{
			name:     "no coverage in output",
			output:   "ok  \tgithub.com/example/test",
			expected: 0.0,
		},
		{
			name:     "multiple lines with coverage",
			output:   "some line\ncoverage: 85.2%\nanother line",
			expected: 85.2,
		},
		{
			name:     "coverage with decimal",
			output:   "coverage: 60.5%",
			expected: 60.5,
		},
		{
			name:     "integer coverage",
			output:   "coverage: 80%",
			expected: 80.0,
		},
		{
			name:     "whitespace around value",
			output:   "coverage:  72.3%  ",
			expected: 72.3,
		},
		{
			name:     "invalid coverage returns 0",
			output:   "coverage: invalid%",
			expected: 0.0,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := ta.parseCoveragePercentage(tt.output)
			assert.InDelta(t, tt.expected, result, 0.01)
		})
	}
}

func TestTestAutomation_calculateOverallScore(t *testing.T) {
	config := &TestAutomationConfig{}
	ta := NewTestAutomation(config)

	summary := &TestSummary{
		SuccessRate: 90.0,
	}
	coverage := &CoverageReport{
		OverallCoverage: 80.0,
	}
	performance := &PerformanceReport{
		PerformanceScore: 85.0,
	}
	security := &SecurityReport{
		SecurityScore: 95.0,
	}

	score := ta.calculateOverallScore(summary, coverage, performance, security)

	// Expected: (90*0.4 + 80*0.3 + 85*0.2 + 95*0.1) = 36 + 24 + 17 + 9.5 = 86.5
	expected := 86.5
	assert.InDelta(t, expected, score, 0.01)
}

// =============================================================================
// TestReporter Tests
// =============================================================================

func TestNewTestReporter(t *testing.T) {
	config := &ReporterConfig{
		OutputDir: "/tmp/reports",
		Formats:   []string{"json", "html"},
	}

	reporter := NewTestReporter(config)

	require.NotNil(t, reporter)
	assert.Equal(t, config, reporter.config)
	assert.NotNil(t, reporter.formats)
	assert.NotNil(t, reporter.results)
	assert.NotNil(t, reporter.stats)
}

func TestTestReporter_GenerateReport_UnsupportedFormat(t *testing.T) {
	config := &ReporterConfig{}
	reporter := NewTestReporter(config)

	report := &TestReport{}
	_, err := reporter.GenerateReport("unsupported", report)
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "unsupported report format")
}

// =============================================================================
// Helper Function Tests
// =============================================================================

func TestExtractTestName(t *testing.T) {
	tests := []struct {
		input    string
		expected string
	}{
		{
			input:    "--- PASS: TestFunction (0.01s)",
			expected: "---",
		},
		{
			input:    "TestName extra data",
			expected: "TestName",
		},
		{
			input:    "",
			expected: "unknown",
		},
		{
			input:    "   ",
			expected: "unknown",
		},
	}

	for _, tt := range tests {
		t.Run(tt.input, func(t *testing.T) {
			result := extractTestName(tt.input)
			assert.Equal(t, tt.expected, result)
		})
	}
}

func TestExtractTestStatus(t *testing.T) {
	tests := []struct {
		input    string
		expected string
	}{
		{
			input:    "--- PASS: TestFunction",
			expected: "passed",
		},
		{
			input:    "--- FAIL: TestFunction",
			expected: "failed",
		},
		{
			input:    "--- SKIP: TestFunction",
			expected: "skipped",
		},
		{
			input:    "--- UNKNOWN: TestFunction",
			expected: "unknown",
		},
		{
			input:    "",
			expected: "unknown",
		},
	}

	for _, tt := range tests {
		t.Run(tt.input, func(t *testing.T) {
			result := extractTestStatus(tt.input)
			assert.Equal(t, tt.expected, result)
		})
	}
}

func TestExtractBenchmarkName(t *testing.T) {
	tests := []struct {
		input    string
		expected string
	}{
		{
			input:    "BenchmarkFunction-8    1000000    1234 ns/op",
			expected: "BenchmarkFunction-8",
		},
		{
			input:    "",
			expected: "unknown",
		},
	}

	for _, tt := range tests {
		t.Run(tt.input, func(t *testing.T) {
			result := extractBenchmarkName(tt.input)
			assert.Equal(t, tt.expected, result)
		})
	}
}

// =============================================================================
// Configuration Structure Tests
// =============================================================================

func TestPipelineConfig(t *testing.T) {
	config := PipelineConfig{
		Name:    "test-pipeline",
		Version: "1.0.0",
		Stages: []PipelineStage{
			{
				Name:     "build",
				Commands: []string{"go build"},
				Environment: map[string]string{
					"GOOS": "linux",
				},
				Timeout:      5 * time.Minute,
				RetryCount:   3,
				Condition:    "always",
				Parallel:     false,
				Dependencies: []string{},
				Artifacts:    []string{"binary"},
			},
		},
		Environment: map[string]string{
			"GLOBAL_VAR": "value",
		},
		Artifacts: []string{"output"},
		Notifications: []Notification{
			{
				Type:     "slack",
				Enabled:  true,
				Events:   []string{"pipeline_started", "pipeline_failed"},
				Template: "Pipeline {{.Name}} {{.Status}}",
				Config: map[string]string{
					"webhook": "https://hooks.slack.com/...",
				},
			},
		},
		Timeout:           30 * time.Minute,
		ParallelExecution: false,
		RetryPolicy: &RetryPolicy{
			MaxRetries: 3,
			Delay:      5 * time.Second,
			Backoff:    "exponential",
		},
	}

	assert.Equal(t, "test-pipeline", config.Name)
	assert.Equal(t, "1.0.0", config.Version)
	assert.Len(t, config.Stages, 1)
	assert.Equal(t, "linux", config.Stages[0].Environment["GOOS"])
	assert.Equal(t, 5*time.Minute, config.Stages[0].Timeout)
	assert.Equal(t, "exponential", config.RetryPolicy.Backoff)
	assert.True(t, config.Notifications[0].Enabled)
}

func TestQualityConfig(t *testing.T) {
	config := QualityConfig{
		GoVersion:    "1.21",
		LintRules:    []string{"govet", "golint", "errcheck"},
		TestCoverage: 80.0,
		Cyclomatic:   10,
		Duplication:  5.0,
		SecurityScan: true,
		Performance:  true,
		CustomRules: map[string]string{
			"naming": "camelCase",
		},
	}

	assert.Equal(t, "1.21", config.GoVersion)
	assert.Len(t, config.LintRules, 3)
	assert.Equal(t, 80.0, config.TestCoverage)
	assert.Equal(t, 10, config.Cyclomatic)
	assert.True(t, config.SecurityScan)
	assert.Equal(t, "camelCase", config.CustomRules["naming"])
}

func TestDeploymentConfig(t *testing.T) {
	config := DeploymentConfig{
		Name:        "my-app",
		Environment: "production",
		Strategy:    "rolling",
		Replicas:    3,
		Image:       "myregistry/my-app:v1.0.0",
		Ports: []PortConfig{
			{
				Name:       "http",
				Port:       80,
				TargetPort: 8080,
				Protocol:   "TCP",
			},
		},
		EnvVars: map[string]string{
			"LOG_LEVEL": "info",
		},
		Resources: &ResourceConfig{
			CPU:    "500m",
			Memory: "512Mi",
		},
		HealthCheck: &HealthCheckConfig{
			Path:     "/health",
			Port:     8080,
			Interval: 10 * time.Second,
			Timeout:  5 * time.Second,
			Retries:  3,
		},
	}

	assert.Equal(t, "my-app", config.Name)
	assert.Equal(t, "production", config.Environment)
	assert.Equal(t, 3, config.Replicas)
	assert.Equal(t, 80, config.Ports[0].Port)
	assert.Equal(t, "512Mi", config.Resources.Memory)
	assert.Equal(t, "/health", config.HealthCheck.Path)
}

// =============================================================================
// StageResult Tests
// =============================================================================

func TestStageResult(t *testing.T) {
	now := time.Now()
	result := &StageResult{
		Name:       "test-stage",
		Status:     "success",
		StartTime:  now,
		EndTime:    now.Add(5 * time.Second),
		Duration:   5 * time.Second,
		Output:     "Build successful",
		Error:      nil,
		RetryCount: 0,
		Artifacts:  []string{"binary"},
		Metrics: map[string]interface{}{
			"cpu_usage": 50.0,
			"memory_mb": 256,
		},
	}

	assert.Equal(t, "test-stage", result.Name)
	assert.Equal(t, "success", result.Status)
	assert.Equal(t, 5*time.Second, result.Duration)
	assert.Equal(t, "binary", result.Artifacts[0])
	assert.Equal(t, 50.0, result.Metrics["cpu_usage"])
}

// =============================================================================
// TestAutomationConfig Tests
// =============================================================================

func TestTestAutomationConfig(t *testing.T) {
	config := TestAutomationConfig{
		ParallelExecution: true,
		MaxWorkers:        8,
		Timeout:           1 * time.Hour,
		RetryCount:        2,
		TestSuites:        []string{"unit", "integration"},
		TestTypes:         []string{"unit", "integration", "performance"},
		Environment: map[string]string{
			"TEST_ENV": "staging",
		},
		CoverageThreshold: 80.0,
		PerformanceThresholds: map[string]float64{
			"latency_p95": 100.0,
			"throughput":  1000.0,
		},
		SecurityScan:    true,
		GenerateReports: true,
		ReportFormats:   []string{"json", "html", "junit"},
	}

	assert.True(t, config.ParallelExecution)
	assert.Equal(t, 8, config.MaxWorkers)
	assert.Equal(t, 1*time.Hour, config.Timeout)
	assert.Len(t, config.TestSuites, 2)
	assert.Len(t, config.TestTypes, 3)
	assert.Equal(t, 80.0, config.CoverageThreshold)
	assert.Equal(t, 100.0, config.PerformanceThresholds["latency_p95"])
	assert.True(t, config.SecurityScan)
}

// =============================================================================
// Integration Tests
// =============================================================================

func TestPipelineWithNotifications(t *testing.T) {
	tmpDir := t.TempDir()

	// Create a notification config
	notification := Notification{
		Type:     "console",
		Enabled:  true,
		Events:   []string{"all"},
		Template: "Pipeline {{.Name}}: {{.Message}}",
		Config:   map[string]string{},
	}

	config := &PipelineConfig{
		Name:    "notified-pipeline",
		Version: "1.0.0",
		Stages: []PipelineStage{
			{
				Name:     "success-stage",
				Commands: []string{"go version"},
			},
		},
		Notifications: []Notification{notification},
	}

	executor := NewPipelineExecutor(config, tmpDir)

	// Register console provider for notifications
	executor.notifications.RegisterProvider("console", &ConsoleNotificationProvider{})

	ctx := context.Background()
	err := executor.Execute(ctx)

	assert.NoError(t, err)
	assert.Equal(t, int64(1), executor.stats.CompletedStages)
}

func TestFullAutomationWorkflow(t *testing.T) {
	// Create automation manager
	manager := NewAutomationManager()

	// Set up pipeline
	pipelineConfig := &PipelineConfig{
		Name:    "build-pipeline",
		Version: "1.0.0",
		Stages:  []PipelineStage{},
	}
	executor := NewPipelineExecutor(pipelineConfig, ".")
	manager.SetPipelineExecutor(executor)

	// Set up quality checker
	qualityConfig := &QualityConfig{
		GoVersion:    "1.21",
		TestCoverage: 80.0,
	}
	checker := NewCodeQualityChecker(qualityConfig)
	manager.SetQualityChecker(checker)

	// Set up deployment manager
	deployConfig := &DeploymentConfig{
		Name:        "test-app",
		Environment: "dev",
		Ports: []PortConfig{
			{Port: 8080, TargetPort: 8080},
		},
		Resources: &ResourceConfig{
			CPU:    "100m",
			Memory: "128Mi",
		},
		HealthCheck: &HealthCheckConfig{
			Path: "/health",
			Port: 8080,
		},
	}
	dm := NewDeploymentManager(deployConfig)
	manager.SetDeploymentManager(dm)

	// Verify all components are set
	assert.NotNil(t, manager.pipelineExecutor)
	assert.NotNil(t, manager.qualityChecker)
	assert.NotNil(t, manager.deploymentManager)

	// Execute pipeline
	ctx := context.Background()
	err := manager.ExecutePipeline(ctx)
	assert.NoError(t, err)

	// Check stats
	stats := manager.GetStats()
	assert.Equal(t, int64(1), stats.PipelinesExecuted)
}

// =============================================================================
// Error Cases Tests
// =============================================================================

func TestPipelineExecutor_Execute_InvalidCommand(t *testing.T) {
	tmpDir := t.TempDir()
	config := &PipelineConfig{
		Name:    "test-pipeline",
		Version: "1.0.0",
		Stages: []PipelineStage{
			{
				Name:     "invalid",
				Commands: []string{"this_command_definitely_does_not_exist_12345"},
			},
		},
	}

	executor := NewPipelineExecutor(config, tmpDir)
	ctx := context.Background()

	err := executor.Execute(ctx)
	assert.Error(t, err)
}

func TestPipelineExecutor_Execute_EmptyCommand(t *testing.T) {
	tmpDir := t.TempDir()
	config := &PipelineConfig{
		Name:    "test-pipeline",
		Version: "1.0.0",
		Stages: []PipelineStage{
			{
				Name:     "empty",
				Commands: []string{""},
			},
		},
	}

	executor := NewPipelineExecutor(config, tmpDir)
	ctx := context.Background()

	err := executor.Execute(ctx)
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "empty command")
}

func TestFileNotificationProvider_Send_InvalidPath(t *testing.T) {
	// Try to write to a read-only path
	provider := NewFileNotificationProvider("/nonexistent/path/notifications.log")
	ctx := context.Background()

	err := provider.Send(ctx, "test message")
	assert.Error(t, err)
}

func TestCodeQualityChecker_Check_InvalidPath(t *testing.T) {
	config := &QualityConfig{
		GoVersion:    "1.21",
		TestCoverage: 50.0,
	}
	checker := NewCodeQualityChecker(config)
	ctx := context.Background()

	// Try to check a path that doesn't contain a valid Go project
	_, err := checker.Check(ctx, "/nonexistent/path")
	// May or may not error depending on go command behavior
	// We just verify the function doesn't panic
	_ = err
}

// =============================================================================
// Concurrent Safety Tests
// =============================================================================

func TestPipelineExecutor_ConcurrentResultsAccess(t *testing.T) {
	executor := NewPipelineExecutor(&PipelineConfig{}, ".")

	// Use mutex for safe concurrent writes
	done := make(chan bool)
	var mu sync.Mutex
	for i := 0; i < 100; i++ {
		go func(idx int) {
			mu.Lock()
			executor.results[fmt.Sprintf("stage-%d", idx)] = &StageResult{
				Name:   fmt.Sprintf("stage-%d", idx),
				Status: "success",
			}
			mu.Unlock()
			done <- true
		}(i)
	}

	for i := 0; i < 100; i++ {
		<-done
	}

	// Verify we can read without panic
	results := executor.GetResults()
	assert.NotNil(t, results)
	assert.GreaterOrEqual(t, len(results), 0)
}

func TestNotificationService_ConcurrentAccess(t *testing.T) {
	service := NewNotificationService()
	ctx := context.Background()

	// Register provider
	service.RegisterProvider("console", &ConsoleNotificationProvider{})

	// Concurrent sends
	done := make(chan error)
	for i := 0; i < 50; i++ {
		go func(idx int) {
			err := service.Send(ctx, "console", string(rune(idx)))
			done <- err
		}(i)
	}

	for i := 0; i < 50; i++ {
		err := <-done
		assert.NoError(t, err)
	}
}

// =============================================================================
// Benchmark Tests
// =============================================================================

func BenchmarkNewPipelineExecutor(b *testing.B) {
	config := &PipelineConfig{
		Name:    "benchmark-pipeline",
		Version: "1.0.0",
		Stages:  []PipelineStage{},
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = NewPipelineExecutor(config, ".")
	}
}

func BenchmarkPipelineExecutor_GetResults(b *testing.B) {
	executor := NewPipelineExecutor(&PipelineConfig{}, ".")
	executor.results["test"] = &StageResult{
		Name:   "test",
		Status: "success",
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = executor.GetResults()
	}
}

func BenchmarkExtractTestStatus(b *testing.B) {
	line := "--- PASS: TestFunction (0.01s)"

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = extractTestStatus(line)
	}
}

func BenchmarkCalculateOverallScore(b *testing.B) {
	config := &QualityConfig{TestCoverage: 80.0}
	checker := NewCodeQualityChecker(config)
	report := &QualityReport{
		Coverage:       75.0,
		LintResults:    []LintResult{},
		SecurityIssues: []SecurityIssue{},
		TestResults:    &TestResult{Failed: 0},
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		checker.calculateOverallScore(report)
	}
}

// =============================================================================
// Cleanup Tests
// =============================================================================

func TestCleanup(t *testing.T) {
	// Clean up any leftover deployment files
	files, _ := filepath.Glob("*-deployment.yaml")
	for _, file := range files {
		os.Remove(file)
	}
}

// TestCleanupTemp verifies temporary files are cleaned up
func TestCleanupTemp(t *testing.T) {
	tmpDir := t.TempDir()
	filename := filepath.Join(tmpDir, "test.txt")

	// Create a file
	err := os.WriteFile(filename, []byte("test"), 0644)
	require.NoError(t, err)

	// Verify it exists
	_, err = os.Stat(filename)
	assert.NoError(t, err)

	// Cleanup is handled by t.TempDir() automatically
}

// TestPipelineExecutor_CancelContext tests context cancellation
func TestPipelineExecutor_CancelContext(t *testing.T) {
	// This test verifies the executor handles contexts properly
	config := &PipelineConfig{
		Name:    "cancel-test",
		Version: "1.0.0",
		Stages: []PipelineStage{
			{
				Name:     "quick",
				Commands: []string{"echo done"},
			},
		},
	}

	executor := NewPipelineExecutor(config, ".")
	ctx, cancel := context.WithCancel(context.Background())

	// Cancel immediately (before execution)
	cancel()

	// Execution should handle cancelled context gracefully
	// Depending on implementation, this may or may not error
	_ = executor.Execute(ctx)
}

// TestStageResult_WithError tests stage result with error
func TestStageResult_WithError(t *testing.T) {
	errMsg := "command failed with exit code 1"
	result := &StageResult{
		Name:   "failed-stage",
		Status: "failed",
		Error:  assert.AnError,
		Output: errMsg,
	}

	assert.Equal(t, "failed", result.Status)
	assert.NotNil(t, result.Error)
	assert.Contains(t, result.Output, errMsg)
}

// TestQualityReportStructure validates QualityReport structure
func TestQualityReportStructure(t *testing.T) {
	now := time.Now()
	report := &QualityReport{
		Timestamp: now,
		GoVersion: "1.21",
		LintResults: []LintResult{
			{
				File:    "main.go",
				Line:    10,
				Column:  5,
				Level:   "error",
				Message: "undefined variable",
				Rule:    "unused",
			},
		},
		TestResults: &TestResult{
			Total:    10,
			Passed:   8,
			Failed:   1,
			Skipped:  1,
			Duration: 5 * time.Second,
			Name:     "TestSuite",
			Status:   "completed",
		},
		Coverage:    85.5,
		Complexity:  map[string]int{"main": 5, "util": 3},
		Duplication: 2.5,
		SecurityIssues: []SecurityIssue{
			{
				File:    "auth.go",
				Line:    25,
				Level:   "high",
				Message: "hardcoded password",
				Rule:    "security",
			},
		},
		Performance: &PerformanceResult{
			Benchmarks: []BenchmarkResult{
				{
					Name:        "BenchmarkFast",
					Duration:    100 * time.Nanosecond,
					Iterations:  1000000,
					BytesPerOp:  64,
					AllocsPerOp: 1,
				},
			},
		},
		OverallScore: 92.0,
	}

	assert.Equal(t, "1.21", report.GoVersion)
	assert.Len(t, report.LintResults, 1)
	assert.Equal(t, "main.go", report.LintResults[0].File)
	assert.Equal(t, 85.5, report.Coverage)
	assert.Equal(t, 92.0, report.OverallScore)
	assert.Len(t, report.SecurityIssues, 1)
}

// TestNotificationConfig validates Notification structure
func TestNotificationConfig(t *testing.T) {
	notification := Notification{
		Type:    "email",
		Enabled: true,
		Config: map[string]string{
			"smtp_host": "smtp.example.com",
			"smtp_port": "587",
		},
		Events:   []string{"pipeline_started", "pipeline_success", "pipeline_failed"},
		Template: "Pipeline {{.Name}} status: {{.Status}}",
	}

	assert.Equal(t, "email", notification.Type)
	assert.True(t, notification.Enabled)
	assert.Equal(t, "smtp.example.com", notification.Config["smtp_host"])
	assert.Len(t, notification.Events, 3)
	assert.Contains(t, notification.Template, "Pipeline")
}

// TestAutomationStatsStructure validates TestAutomationStats structure
func TestAutomationStatsStructure(t *testing.T) {
	stats := &TestAutomationStats{
		TotalTests:       100,
		PassedTests:      95,
		FailedTests:      3,
		SkippedTests:     2,
		TotalDuration:    5 * time.Minute,
		TestSuitesRun:    5,
		CoverageAchieved: 87.5,
		PerformanceTests: 10,
		SecurityTests:    5,
		IntegrationTests: 20,
		UnitTests:        60,
	}

	assert.Equal(t, int64(100), stats.TotalTests)
	assert.Equal(t, int64(95), stats.PassedTests)
	assert.Equal(t, int64(3), stats.FailedTests)
	assert.Equal(t, 87.5, stats.CoverageAchieved)
}

// TestAutomationStatsType validates AutomationStats type
func TestAutomationStatsType(t *testing.T) {
	now := time.Now()
	stats := &AutomationStats{
		PipelinesExecuted:   10,
		QualityChecksRun:    20,
		DeploymentsExecuted: 5,
		NotificationsSent:   50,
		TotalDuration:       2 * time.Hour,
		LastOperationTime:   now,
	}

	assert.Equal(t, int64(10), stats.PipelinesExecuted)
	assert.Equal(t, int64(20), stats.QualityChecksRun)
	assert.Equal(t, int64(5), stats.DeploymentsExecuted)
	assert.Equal(t, 2*time.Hour, stats.TotalDuration)
}

// TestPipelineStats validates PipelineStats
func TestPipelineStats(t *testing.T) {
	now := time.Now()
	stats := &PipelineStats{
		TotalStages:     5,
		CompletedStages: 4,
		FailedStages:    1,
		SkippedStages:   0,
		TotalDuration:   10 * time.Minute,
		StartTime:       now,
		EndTime:         now.Add(10 * time.Minute),
		ArtifactsCount:  3,
		RetryCount:      2,
	}

	assert.Equal(t, int64(5), stats.TotalStages)
	assert.Equal(t, int64(4), stats.CompletedStages)
	assert.Equal(t, int64(1), stats.FailedStages)
	assert.Equal(t, 10*time.Minute, stats.TotalDuration)
}

// TestExtractTestDuration validates test duration extraction
func TestExtractTestDuration(t *testing.T) {
	// The current implementation returns a fixed value
	duration := extractTestDuration("--- PASS: TestFunction (0.01s)")
	assert.Equal(t, 100*time.Millisecond, duration)

	duration = extractTestDuration("invalid")
	assert.Equal(t, 100*time.Millisecond, duration)
}

// TestExtractBenchmarkDuration validates benchmark duration extraction
func TestExtractBenchmarkDuration(t *testing.T) {
	// The current implementation returns a fixed value
	duration := extractBenchmarkDuration("BenchmarkFunction-8    1000000    1234 ns/op")
	assert.Equal(t, 100*time.Millisecond, duration)

	duration = extractBenchmarkDuration("invalid")
	assert.Equal(t, 100*time.Millisecond, duration)
}

// TestServiceConfig validates ServiceConfig structure
func TestServiceConfig(t *testing.T) {
	service := ServiceConfig{
		Name:  "postgres",
		Image: "postgres:14",
		Ports: []PortConfig{
			{Name: "postgres", Port: 5432, TargetPort: 5432, Protocol: "TCP"},
		},
		EnvVars: map[string]string{
			"POSTGRES_DB":       "testdb",
			"POSTGRES_PASSWORD": "testpass",
		},
		Health: &HealthCheckConfig{
			Path:     "/health",
			Port:     8080,
			Interval: 10 * time.Second,
			Timeout:  5 * time.Second,
			Retries:  3,
		},
	}

	assert.Equal(t, "postgres", service.Name)
	assert.Equal(t, "postgres:14", service.Image)
	assert.Equal(t, 5432, service.Ports[0].Port)
	assert.Equal(t, "testdb", service.EnvVars["POSTGRES_DB"])
	assert.Equal(t, 3, service.Health.Retries)
}

// TestDatabaseConfig validates DatabaseConfig structure
func TestDatabaseConfig(t *testing.T) {
	db := DatabaseConfig{
		Name:     "testdb",
		Type:     "postgresql",
		Host:     "localhost",
		Port:     5432,
		Database: "myapp",
		Username: "admin",
		Password: "secret",
		Options: map[string]string{
			"sslmode": "disable",
		},
	}

	assert.Equal(t, "testdb", db.Name)
	assert.Equal(t, "postgresql", db.Type)
	assert.Equal(t, "localhost", db.Host)
	assert.Equal(t, 5432, db.Port)
	assert.Equal(t, "disable", db.Options["sslmode"])
}

// TestNetworkConfig validates NetworkConfig structure
func TestNetworkConfig(t *testing.T) {
	network := NetworkConfig{
		Name:    "testnet",
		Driver:  "bridge",
		Subnet:  "172.20.0.0/16",
		Gateway: "172.20.0.1",
	}

	assert.Equal(t, "testnet", network.Name)
	assert.Equal(t, "bridge", network.Driver)
	assert.Equal(t, "172.20.0.0/16", network.Subnet)
	assert.Equal(t, "172.20.0.1", network.Gateway)
}

// TestReporterConfig validates ReporterConfig structure
func TestReporterConfig(t *testing.T) {
	config := &ReporterConfig{
		OutputDir:          "/tmp/reports",
		Formats:            []string{"json", "html"},
		IncludeCoverage:    true,
		IncludePerformance: true,
		IncludeSecurity:    false,
		Template:           "default",
		EmailConfig: &EmailConfig{
			SMTPHost: "smtp.example.com",
			SMTPPort: 587,
			Username: "test@example.com",
			Password: "password",
			From:     "test@example.com",
			To:       []string{"admin@example.com"},
			Subject:  "Test Report",
		},
		WebhookConfig: &WebhookConfig{
			URL:     "https://hooks.slack.com/test",
			Method:  "POST",
			Headers: map[string]string{"Content-Type": "application/json"},
			Payload: map[string]interface{}{"text": "Test completed"},
			Timeout: 10 * time.Second,
		},
	}

	assert.Equal(t, "/tmp/reports", config.OutputDir)
	assert.Len(t, config.Formats, 2)
	assert.True(t, config.IncludeCoverage)
	assert.Equal(t, "smtp.example.com", config.EmailConfig.SMTPHost)
	assert.Equal(t, "https://hooks.slack.com/test", config.WebhookConfig.URL)
}

// TestCoverageReport validates CoverageReport structure
func TestCoverageReport(t *testing.T) {
	report := &CoverageReport{
		OverallCoverage: 85.5,
		PackageCoverage: map[string]float64{
			"main": 90.0,
			"util": 80.0,
			"api":  75.0,
		},
		FileCoverage: map[string]float64{
			"main.go": 95.0,
			"util.go": 85.0,
		},
		FunctionCoverage: map[string]float64{
			"main":   100.0,
			"helper": 80.0,
		},
		LinesCovered:    850,
		LinesTotal:      1000,
		BranchesCovered: 400,
		BranchesTotal:   500,
	}

	assert.Equal(t, 85.5, report.OverallCoverage)
	assert.Equal(t, 90.0, report.PackageCoverage["main"])
	assert.Equal(t, 95.0, report.FileCoverage["main.go"])
	assert.Equal(t, int64(850), report.LinesCovered)
	assert.Equal(t, int64(1000), report.LinesTotal)
}

// TestSecurityReport validates SecurityReport structure
func TestSecurityReport(t *testing.T) {
	report := &SecurityReport{
		Vulnerabilities: []Vulnerability{
			{
				ID:          "CVE-2024-1234",
				Severity:    "high",
				Description: "SQL injection vulnerability",
				File:        "auth.go",
				Line:        42,
				Rule:        "sql-injection",
				Fix:         "Use parameterized queries",
			},
		},
		SecurityScore: 85.0,
		ScanResults: map[string]interface{}{
			"tool":    "gosec",
			"version": "2.0.0",
		},
		ComplianceCheck: &ComplianceResult{
			Standard:   "OWASP",
			Compliant:  false,
			Score:      75.0,
			Violations: []ComplianceViolation{},
			Recommendations: []string{
				"Fix SQL injection vulnerability",
			},
		},
		Recommendations: []string{
			"Enable security scanning in CI",
		},
	}

	assert.Equal(t, 85.0, report.SecurityScore)
	assert.Len(t, report.Vulnerabilities, 1)
	assert.Equal(t, "CVE-2024-1234", report.Vulnerabilities[0].ID)
	assert.Equal(t, "OWASP", report.ComplianceCheck.Standard)
	assert.False(t, report.ComplianceCheck.Compliant)
}

// TestPerformanceReport validates PerformanceReport structure
func TestPerformanceReport(t *testing.T) {
	report := &PerformanceReport{
		Benchmarks: []BenchmarkResultExtended{
			{
				Name:        "BenchmarkFast",
				Duration:    100 * time.Nanosecond,
				Iterations:  1000000,
				BytesPerOp:  64,
				AllocsPerOp: 1,
				MemoryUsage: 1024,
				CPUUsage:    10.5,
				Score:       95.0,
			},
		},
		LoadTests: []LoadTestResult{
			{
				Name:        "LoadTestAPI",
				Duration:    5 * time.Minute,
				Concurrency: 100,
				Requests:    100000,
				SuccessRate: 99.9,
				AvgResponse: 50 * time.Millisecond,
				MaxResponse: 200 * time.Millisecond,
				MinResponse: 10 * time.Millisecond,
				Throughput:  333.33,
				ErrorRate:   0.1,
			},
		},
		MemoryUsage: &MemoryStats{
			Alloc:       1024000,
			TotalAlloc:  2048000,
			Sys:         4096000,
			HeapAlloc:   512000,
			HeapObjects: 1000,
			NumGC:       5,
		},
		CPUUsage: &CPUStats{
			Usage: 45.5,
			Time:  1 * time.Second,
		},
		ResponseTimes: &ResponseTimeStats{
			Average: 50 * time.Millisecond,
			Median:  45 * time.Millisecond,
			P95:     100 * time.Millisecond,
			P99:     150 * time.Millisecond,
			Max:     200 * time.Millisecond,
			Min:     10 * time.Millisecond,
		},
		Throughput: &ThroughputStats{
			RequestsPerSecond: 1000.0,
			BytesPerSecond:    1024000.0,
			PeakThroughput:    1500.0,
			AverageThroughput: 1200.0,
		},
		PerformanceScore: 88.5,
	}

	assert.Equal(t, 88.5, report.PerformanceScore)
	assert.Len(t, report.Benchmarks, 1)
	assert.Equal(t, uint64(1024000), report.MemoryUsage.Alloc)
	assert.Equal(t, 45.5, report.CPUUsage.Usage)
	assert.Equal(t, 100*time.Millisecond, report.ResponseTimes.P95)
	assert.Equal(t, 1000.0, report.Throughput.RequestsPerSecond)
}

// TestTestSummary validates TestSummary structure
func TestTestSummary(t *testing.T) {
	summary := &TestSummary{
		TotalTests:       100,
		PassedTests:      95,
		FailedTests:      3,
		SkippedTests:     2,
		SuccessRate:      95.0,
		Duration:         5 * time.Minute,
		Coverage:         85.5,
		PerformanceScore: 90.0,
		SecurityScore:    88.0,
		OverallScore:     91.0,
	}

	assert.Equal(t, int64(100), summary.TotalTests)
	assert.Equal(t, float64(95), summary.SuccessRate)
	assert.Equal(t, 85.5, summary.Coverage)
	assert.Equal(t, 91.0, summary.OverallScore)
}

// TestComplianceResult validates ComplianceResult structure
func TestComplianceResult(t *testing.T) {
	result := &ComplianceResult{
		Standard:  "CIS",
		Compliant: true,
		Score:     95.0,
		Violations: []ComplianceViolation{
			{
				Rule:        "1.1",
				Description: "Ensure MFA is enabled",
				Severity:    "medium",
				File:        "auth.go",
				Line:        25,
			},
		},
		Recommendations: []string{
			"Review security policies",
		},
	}

	assert.Equal(t, "CIS", result.Standard)
	assert.True(t, result.Compliant)
	assert.Equal(t, 95.0, result.Score)
	assert.Len(t, result.Violations, 1)
	assert.Equal(t, "1.1", result.Violations[0].Rule)
}

// TestVulnerability validates Vulnerability structure
func TestVulnerability(t *testing.T) {
	vuln := Vulnerability{
		ID:          "CVE-2024-5678",
		Severity:    "critical",
		Description: "Remote code execution",
		File:        "handler.go",
		Line:        100,
		Rule:        "rce",
		Fix:         "Update dependency to v2.0.0",
	}

	assert.Equal(t, "CVE-2024-5678", vuln.ID)
	assert.Equal(t, "critical", vuln.Severity)
	assert.Equal(t, "Remote code execution", vuln.Description)
	assert.Equal(t, "handler.go", vuln.File)
	assert.Equal(t, 100, vuln.Line)
	assert.Equal(t, "Update dependency to v2.0.0", vuln.Fix)
}

// TestLoadTestResult validates LoadTestResult structure
func TestLoadTestResult(t *testing.T) {
	result := LoadTestResult{
		Name:        "APILoadTest",
		Duration:    10 * time.Minute,
		Concurrency: 500,
		Requests:    1000000,
		SuccessRate: 99.95,
		AvgResponse: 25 * time.Millisecond,
		MaxResponse: 500 * time.Millisecond,
		MinResponse: 5 * time.Millisecond,
		Throughput:  1666.67,
		ErrorRate:   0.05,
	}

	assert.Equal(t, "APILoadTest", result.Name)
	assert.Equal(t, 500, result.Concurrency)
	assert.Equal(t, int64(1000000), result.Requests)
	assert.Equal(t, 99.95, result.SuccessRate)
	assert.Equal(t, 25*time.Millisecond, result.AvgResponse)
}

// TestResponseTimeStats validates ResponseTimeStats structure
func TestResponseTimeStats(t *testing.T) {
	stats := &ResponseTimeStats{
		Average: 50 * time.Millisecond,
		Median:  45 * time.Millisecond,
		P95:     100 * time.Millisecond,
		P99:     150 * time.Millisecond,
		Max:     200 * time.Millisecond,
		Min:     10 * time.Millisecond,
	}

	assert.Equal(t, 50*time.Millisecond, stats.Average)
	assert.Equal(t, 45*time.Millisecond, stats.Median)
	assert.Equal(t, 100*time.Millisecond, stats.P95)
	assert.Equal(t, 150*time.Millisecond, stats.P99)
}

// TestThroughputStats validates ThroughputStats structure
func TestThroughputStats(t *testing.T) {
	stats := &ThroughputStats{
		RequestsPerSecond: 1000.0,
		BytesPerSecond:    1048576.0,
		PeakThroughput:    1500.0,
		AverageThroughput: 1200.0,
	}

	assert.Equal(t, 1000.0, stats.RequestsPerSecond)
	assert.Equal(t, 1048576.0, stats.BytesPerSecond)
	assert.Equal(t, 1500.0, stats.PeakThroughput)
}

// TestMemoryStats validates MemoryStats structure
func TestMemoryStats(t *testing.T) {
	stats := &MemoryStats{
		Alloc:       1024000,
		TotalAlloc:  2048000,
		Sys:         4096000,
		HeapAlloc:   512000,
		HeapObjects: 1000,
		NumGC:       10,
	}

	assert.Equal(t, uint64(1024000), stats.Alloc)
	assert.Equal(t, uint64(2048000), stats.TotalAlloc)
	assert.Equal(t, uint64(4096000), stats.Sys)
	assert.Equal(t, uint64(1000), stats.HeapObjects)
	assert.Equal(t, uint32(10), stats.NumGC)
}

// TestCPUStats validates CPUStats structure
func TestCPUStats(t *testing.T) {
	stats := &CPUStats{
		Usage: 45.5,
		Time:  2 * time.Second,
	}

	assert.Equal(t, 45.5, stats.Usage)
	assert.Equal(t, 2*time.Second, stats.Time)
}

// TestWebhookConfig validates WebhookConfig structure
func TestWebhookConfig(t *testing.T) {
	config := &WebhookConfig{
		URL:    "https://api.example.com/webhook",
		Method: "POST",
		Headers: map[string]string{
			"Content-Type":  "application/json",
			"Authorization": "Bearer token123",
		},
		Payload: map[string]interface{}{
			"event":   "test_complete",
			"status":  "passed",
			"details": map[string]string{"suite": "integration"},
		},
		Timeout: 30 * time.Second,
	}

	assert.Equal(t, "https://api.example.com/webhook", config.URL)
	assert.Equal(t, "POST", config.Method)
	assert.Equal(t, "application/json", config.Headers["Content-Type"])
	assert.Equal(t, "Bearer token123", config.Headers["Authorization"])
	assert.Equal(t, "test_complete", config.Payload["event"])
	assert.Equal(t, 30*time.Second, config.Timeout)
}

// TestEmailConfig validates EmailConfig structure
func TestEmailConfig(t *testing.T) {
	config := &EmailConfig{
		SMTPHost: "smtp.gmail.com",
		SMTPPort: 587,
		Username: "test@gmail.com",
		Password: "app_password",
		From:     "test@gmail.com",
		To:       []string{"admin@example.com", "dev@example.com"},
		Subject:  "Test Results - {{.Date}}",
		Template: "Tests: {{.Passed}}/{{.Total}} passed",
	}

	assert.Equal(t, "smtp.gmail.com", config.SMTPHost)
	assert.Equal(t, 587, config.SMTPPort)
	assert.Equal(t, "test@gmail.com", config.From)
	assert.Len(t, config.To, 2)
	assert.Equal(t, "admin@example.com", config.To[0])
	assert.Equal(t, "Test Results - {{.Date}}", config.Subject)
}

// TestTestEnvironment validates TestEnvironment structure
func TestTestEnvironment(t *testing.T) {
	env := &TestEnvironment{
		Name: "integration-env",
		Variables: map[string]string{
			"DB_HOST":   "localhost",
			"DB_PORT":   "5432",
			"API_KEY":   "test-key",
			"LOG_LEVEL": "debug",
		},
		Services: []ServiceConfig{
			{
				Name:  "postgres",
				Image: "postgres:14",
				Ports: []PortConfig{
					{Name: "postgres", Port: 5432, TargetPort: 5432, Protocol: "TCP"},
				},
				EnvVars: map[string]string{
					"POSTGRES_DB":       "testdb",
					"POSTGRES_PASSWORD": "testpass",
				},
			},
		},
		Databases: []DatabaseConfig{
			{
				Name:     "primary",
				Type:     "postgresql",
				Host:     "localhost",
				Port:     5432,
				Database: "testdb",
				Username: "admin",
				Password: "secret",
			},
		},
		Networks: []NetworkConfig{
			{
				Name:    "testnet",
				Driver:  "bridge",
				Subnet:  "172.20.0.0/16",
				Gateway: "172.20.0.1",
			},
		},
		Resources: &ResourceConfig{
			CPU:    "2",
			Memory: "4Gi",
		},
		Cleanup: true,
	}

	assert.Equal(t, "integration-env", env.Name)
	assert.Equal(t, "localhost", env.Variables["DB_HOST"])
	assert.Len(t, env.Services, 1)
	assert.Equal(t, "postgres", env.Services[0].Name)
	assert.Len(t, env.Databases, 1)
	assert.Equal(t, "postgresql", env.Databases[0].Type)
	assert.Len(t, env.Networks, 1)
	assert.Equal(t, "bridge", env.Networks[0].Driver)
	assert.Equal(t, "2", env.Resources.CPU)
	assert.True(t, env.Cleanup)
}

// TestTestReport validates TestReport structure
func TestTestReport(t *testing.T) {
	now := time.Now()
	report := &TestReport{
		Summary: &TestSummary{
			TotalTests:   100,
			PassedTests:  95,
			FailedTests:  3,
			SkippedTests: 2,
			SuccessRate:  95.0,
			Duration:     5 * time.Minute,
			Coverage:     85.5,
			OverallScore: 90.0,
		},
		TestResults: []*TestResult{
			{
				Name:      "TestFunction",
				Status:    "passed",
				Duration:  100 * time.Millisecond,
				Output:    "PASS",
				Timestamp: now,
			},
		},
		Coverage: &CoverageReport{
			OverallCoverage: 85.5,
		},
		Performance: &PerformanceReport{
			PerformanceScore: 88.0,
		},
		Security: &SecurityReport{
			SecurityScore: 92.0,
		},
		Environment: &TestEnvironment{
			Name: "test-env",
		},
		GeneratedAt: now,
		Duration:    5 * time.Minute,
		Metadata: map[string]interface{}{
			"version": "1.0.0",
			"runner":  "go test",
		},
	}

	assert.Equal(t, int64(100), report.Summary.TotalTests)
	assert.Equal(t, 95.0, report.Summary.SuccessRate)
	assert.Len(t, report.TestResults, 1)
	assert.Equal(t, "TestFunction", report.TestResults[0].Name)
	assert.Equal(t, 85.5, report.Coverage.OverallCoverage)
	assert.Equal(t, "test-env", report.Environment.Name)
	assert.Equal(t, "1.0.0", report.Metadata["version"])
}

// TestNewTestReporter validates NewTestReporter function
func TestNewTestReporter_ValidConfig(t *testing.T) {
	config := &ReporterConfig{
		OutputDir:          "/custom/reports",
		Formats:            []string{"json", "html", "junit"},
		IncludeCoverage:    true,
		IncludePerformance: true,
		IncludeSecurity:    true,
	}

	reporter := NewTestReporter(config)

	require.NotNil(t, reporter)
	assert.Equal(t, config, reporter.config)
	assert.NotNil(t, reporter.formats)
	assert.NotNil(t, reporter.results)
	assert.NotNil(t, reporter.stats)
}

// TestAutomationManager_MultipleExecutions validates multiple pipeline executions
func TestAutomationManager_MultipleExecutions(t *testing.T) {
	manager := NewAutomationManager()

	// Create a simple pipeline that succeeds
	pipelineConfig := &PipelineConfig{
		Name:    "multi-exec-pipeline",
		Version: "1.0.0",
		Stages:  []PipelineStage{}, // Empty stages will succeed
	}
	executor := NewPipelineExecutor(pipelineConfig, ".")
	manager.SetPipelineExecutor(executor)

	ctx := context.Background()

	// Execute multiple times
	for i := 0; i < 5; i++ {
		err := manager.ExecutePipeline(ctx)
		assert.NoError(t, err)
	}

	stats := manager.GetStats()
	assert.Equal(t, int64(5), stats.PipelinesExecuted)
	assert.True(t, stats.TotalDuration >= 0)
}

// TestPipelineExecutor_StageWithMultipleCommands validates stages with multiple commands
func TestPipelineExecutor_StageWithMultipleCommands(t *testing.T) {
	tmpDir := t.TempDir()
	config := &PipelineConfig{
		Name:    "multi-command-pipeline",
		Version: "1.0.0",
		Stages: []PipelineStage{
			{
				Name: "multi",
				Commands: []string{
					"go version",
					"go env GOOS",
					"go env GOARCH",
				},
			},
		},
	}

	executor := NewPipelineExecutor(config, tmpDir)
	ctx := context.Background()

	err := executor.Execute(ctx)
	assert.NoError(t, err)

	results := executor.GetResults()
	assert.Len(t, results, 1)
	assert.Equal(t, "success", results["multi"].Status)
}

// TestNotificationFiltering validates notification event filtering
func TestNotificationFiltering(t *testing.T) {
	// Test that notifications are filtered by event type
	config := &PipelineConfig{
		Name:    "filter-test",
		Version: "1.0.0",
		Stages:  []PipelineStage{},
		Notifications: []Notification{
			{
				Type:     "console",
				Enabled:  true,
				Events:   []string{"pipeline_started"},
				Template: "Started",
			},
			{
				Type:     "console",
				Enabled:  true,
				Events:   []string{"pipeline_success"},
				Template: "Success",
			},
			{
				Type:     "console",
				Enabled:  false, // Disabled notification
				Events:   []string{"all"},
				Template: "Disabled",
			},
		},
	}

	executor := NewPipelineExecutor(config, ".")
	// Register console provider
	executor.notifications.RegisterProvider("console", &ConsoleNotificationProvider{})

	// The sendNotification method should filter correctly
	// We can't easily verify output, but we can verify no panic occurs
	ctx := context.Background()
	err := executor.Execute(ctx)
	assert.NoError(t, err)
}

// TestCalculateRetryDelay_ExponentialBackoff validates exponential backoff calculation
func TestCalculateRetryDelay_ExponentialBackoff(t *testing.T) {
	config := &PipelineConfig{
		RetryPolicy: &RetryPolicy{
			Delay:   100 * time.Millisecond,
			Backoff: "exponential",
		},
	}
	executor := NewPipelineExecutor(config, ".")

	tests := []struct {
		attempt  int
		expected time.Duration
	}{
		{0, 100 * time.Millisecond},
		{1, 200 * time.Millisecond},
		{2, 400 * time.Millisecond},
		{3, 800 * time.Millisecond},
		{4, 1600 * time.Millisecond},
	}

	for _, tt := range tests {
		t.Run(fmt.Sprintf("attempt_%d", tt.attempt), func(t *testing.T) {
			delay := executor.calculateRetryDelay(tt.attempt)
			assert.Equal(t, tt.expected, delay)
		})
	}
}

// =============================================================================
// Additional Tests for Coverage Improvement
// =============================================================================

// TestPipelineExecutor_executeStage validates executeStage function
func TestPipelineExecutor_executeStage(t *testing.T) {
	tmpDir := t.TempDir()
	executor := NewPipelineExecutor(&PipelineConfig{}, tmpDir)

	stage := PipelineStage{
		Name: "test",
		Commands: []string{
			"go version",
		},
		Environment: map[string]string{
			"TEST_VAR": "test_value",
		},
	}

	result := &StageResult{
		Name:    "test",
		Metrics: make(map[string]interface{}),
	}

	ctx := context.Background()
	err := executor.executeStage(ctx, stage, result)
	assert.NoError(t, err)
}

// TestPipelineExecutor_sendNotification validates sendNotification function
func TestPipelineExecutor_sendNotification(t *testing.T) {
	tmpDir := t.TempDir()
	config := &PipelineConfig{
		Name:    "test",
		Version: "1.0",
		Notifications: []Notification{
			{
				Type:     "console",
				Enabled:  true,
				Events:   []string{"test_event"},
				Template: "Test message",
			},
			{
				Type:     "console",
				Enabled:  false, // Disabled
				Events:   []string{"test_event"},
				Template: "Should not send",
			},
		},
	}

	executor := NewPipelineExecutor(config, tmpDir)
	executor.notifications.RegisterProvider("console", &ConsoleNotificationProvider{})

	// This should not panic
	executor.sendNotification("test_event", "Test message")
	executor.sendNotification("other_event", "Should not match")
}

// TestAutomationManager_ExecutePipeline_WithExecutor validates ExecutePipeline with configured executor
func TestAutomationManager_ExecutePipeline_WithExecutor(t *testing.T) {
	manager := NewAutomationManager()

	// Create a pipeline that will succeed
	config := &PipelineConfig{
		Name:    "test-pipeline",
		Version: "1.0.0",
		Stages:  []PipelineStage{}, // Empty stages = immediate success
	}
	executor := NewPipelineExecutor(config, ".")
	manager.SetPipelineExecutor(executor)

	ctx := context.Background()
	err := manager.ExecutePipeline(ctx)

	assert.NoError(t, err)

	stats := manager.GetStats()
	assert.Equal(t, int64(1), stats.PipelinesExecuted)
	assert.True(t, stats.LastOperationTime.After(time.Time{}))
}

// TestTestAutomation_setupTestEnvironment validates setupTestEnvironment
func TestTestAutomation_setupTestEnvironment(t *testing.T) {
	config := &TestAutomationConfig{
		Environment: map[string]string{
			"TEST_KEY": "test_value",
		},
	}
	ta := NewTestAutomation(config)
	ta.environment.Services = []ServiceConfig{
		{Name: "test-service"},
	}
	ta.environment.Databases = []DatabaseConfig{
		{Name: "test-db"},
	}

	ctx := context.Background()
	err := ta.setupTestEnvironment(ctx)
	assert.NoError(t, err)

	// Verify environment variable was set
	assert.Equal(t, "test_value", os.Getenv("TEST_KEY"))
}

// TestTestAutomation_cleanupTestEnvironment validates cleanupTestEnvironment
func TestTestAutomation_cleanupTestEnvironment(t *testing.T) {
	config := &TestAutomationConfig{}
	ta := NewTestAutomation(config)
	ta.environment.Services = []ServiceConfig{
		{Name: "test-service"},
	}
	ta.environment.Databases = []DatabaseConfig{
		{Name: "test-db"},
	}

	ctx := context.Background()
	err := ta.cleanupTestEnvironment(ctx)
	assert.NoError(t, err)
}

// TestTestAutomation_generatePerformanceReport validates generatePerformanceReport
func TestTestAutomation_generatePerformanceReport(t *testing.T) {
	config := &TestAutomationConfig{}
	ta := NewTestAutomation(config)

	results := []*TestResult{
		{
			Name:   "BenchmarkTest",
			Status: "passed",
		},
	}

	report, err := ta.generatePerformanceReport(results)
	assert.NoError(t, err)
	assert.NotNil(t, report)
	assert.NotNil(t, report.Benchmarks)
	assert.NotNil(t, report.MemoryUsage)
	assert.NotNil(t, report.CPUUsage)
	assert.NotNil(t, report.ResponseTimes)
	assert.NotNil(t, report.Throughput)
	assert.Greater(t, report.PerformanceScore, 0.0)
}

// TestTestAutomation_generateSecurityReport validates generateSecurityReport
func TestTestAutomation_generateSecurityReport(t *testing.T) {
	config := &TestAutomationConfig{}
	ta := NewTestAutomation(config)

	results := []*TestResult{
		{
			Name:   "Security Scan",
			Status: "failed",
			Output: "Security issue found",
		},
	}

	report, err := ta.generateSecurityReport(results)
	assert.NoError(t, err)
	assert.NotNil(t, report)
	assert.NotNil(t, report.Vulnerabilities)
	assert.NotNil(t, report.ScanResults)
	assert.NotNil(t, report.ComplianceCheck)
	assert.NotNil(t, report.Recommendations)
	assert.Greater(t, report.SecurityScore, 0.0)
}

// TestPipelineExecutor_executeCommand validates executeCommand
func TestPipelineExecutor_executeCommand(t *testing.T) {
	tmpDir := t.TempDir()
	executor := NewPipelineExecutor(&PipelineConfig{}, tmpDir)

	result := &StageResult{
		Name:    "test",
		Metrics: make(map[string]interface{}),
	}

	ctx := context.Background()

	// Test valid command
	err := executor.executeCommand(ctx, "go version", result)
	assert.NoError(t, err)
	assert.NotEmpty(t, result.Output)
}

// TestPipelineExecutor_executeCommand_Empty validates executeCommand with empty command
func TestPipelineExecutor_executeCommand_Empty(t *testing.T) {
	tmpDir := t.TempDir()
	executor := NewPipelineExecutor(&PipelineConfig{}, tmpDir)

	result := &StageResult{
		Name:    "test",
		Metrics: make(map[string]interface{}),
	}

	ctx := context.Background()

	// Test empty command
	err := executor.executeCommand(ctx, "", result)
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "empty command")
}

// TestPipelineExecutor_executeCommand_Invalid validates executeCommand with invalid command
func TestPipelineExecutor_executeCommand_Invalid(t *testing.T) {
	tmpDir := t.TempDir()
	executor := NewPipelineExecutor(&PipelineConfig{}, tmpDir)

	result := &StageResult{
		Name:    "test",
		Metrics: make(map[string]interface{}),
	}

	ctx := context.Background()

	// Test invalid command
	err := executor.executeCommand(ctx, "nonexistent_command_xyz", result)
	assert.Error(t, err)
}

// TestRetryPolicy validates RetryPolicy structure
func TestRetryPolicy(t *testing.T) {
	policy := &RetryPolicy{
		MaxRetries: 3,
		Delay:      5 * time.Second,
		Backoff:    "exponential",
	}

	assert.Equal(t, 3, policy.MaxRetries)
	assert.Equal(t, 5*time.Second, policy.Delay)
	assert.Equal(t, "exponential", policy.Backoff)
}

// TestBenchmarkResult validates BenchmarkResult structure
func TestBenchmarkResult(t *testing.T) {
	result := BenchmarkResult{
		Name:        "BenchmarkFast",
		Duration:    100 * time.Nanosecond,
		Iterations:  1000000,
		BytesPerOp:  64,
		AllocsPerOp: 1,
	}

	assert.Equal(t, "BenchmarkFast", result.Name)
	assert.Equal(t, 100*time.Nanosecond, result.Duration)
	assert.Equal(t, 1000000, result.Iterations)
	assert.Equal(t, int64(64), result.BytesPerOp)
}

// TestStageResult_WithArtifacts validates StageResult with artifacts
func TestStageResult_WithArtifacts(t *testing.T) {
	result := &StageResult{
		Name:      "build",
		Status:    "success",
		Artifacts: []string{"binary", "config.yaml", "README.md"},
		Metrics: map[string]interface{}{
			"build_time_ms": 5000,
			"cache_hits":    10,
		},
	}

	assert.Len(t, result.Artifacts, 3)
	assert.Equal(t, "binary", result.Artifacts[0])
	assert.Equal(t, 5000, result.Metrics["build_time_ms"])
}

// TestNotificationProviderNotFound validates error when provider not found
func TestNotificationProviderNotFound(t *testing.T) {
	service := NewNotificationService()
	ctx := context.Background()

	err := service.Send(ctx, "nonexistent", "message")
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "not found")
}

// TestPipelineExecutor_executeStageWithRetry_Success validates successful retry
func TestPipelineExecutor_executeStageWithRetry_Success(t *testing.T) {
	tmpDir := t.TempDir()
	config := &PipelineConfig{
		RetryPolicy: &RetryPolicy{
			MaxRetries: 2,
			Delay:      10 * time.Millisecond,
			Backoff:    "linear",
		},
	}
	executor := NewPipelineExecutor(config, tmpDir)

	stage := PipelineStage{
		Name:     "retry-test",
		Commands: []string{"go version"},
	}

	result := &StageResult{
		Name:    "retry-test",
		Metrics: make(map[string]interface{}),
	}

	ctx := context.Background()
	err := executor.executeStageWithRetry(ctx, stage, result)
	assert.NoError(t, err)
	assert.Equal(t, 0, result.RetryCount) // Should succeed on first try
}

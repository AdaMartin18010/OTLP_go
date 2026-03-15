package resource

import (
	"context"
	"os"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestDetectCloudProvider(t *testing.T) {
	// This test's result depends on the environment
	// Just ensure it doesn't panic and returns a valid value
	provider := DetectCloudProvider()
	assert.True(t, provider >= CloudProviderUnknown && provider <= CloudProviderAzure)
}

func TestCloudProviderString(t *testing.T) {
	tests := []struct {
		provider CloudProvider
		expected string
	}{
		{CloudProviderUnknown, "unknown"},
		{CloudProviderAWS, "aws"},
		{CloudProviderGCP, "gcp"},
		{CloudProviderAzure, "azure"},
	}

	for _, tt := range tests {
		t.Run(tt.expected, func(t *testing.T) {
			assert.Equal(t, tt.expected, tt.provider.String())
		})
	}
}

func TestIsAWS(t *testing.T) {
	t.Run("detects from environment variable", func(t *testing.T) {
		os.Setenv("AWS_REGION", "us-east-1")
		defer os.Unsetenv("AWS_REGION")

		assert.True(t, isAWS())
	})

	t.Run("detects from AWS_DEFAULT_REGION", func(t *testing.T) {
		os.Setenv("AWS_DEFAULT_REGION", "us-west-2")
		defer os.Unsetenv("AWS_DEFAULT_REGION")

		assert.True(t, isAWS())
	})

	t.Run("no AWS without env vars", func(t *testing.T) {
		os.Unsetenv("AWS_REGION")
		os.Unsetenv("AWS_DEFAULT_REGION")

		// Result depends on whether metadata service is reachable
		// Just ensure it doesn't panic
		_ = isAWS()
	})
}

func TestIsGCP(t *testing.T) {
	t.Run("detects from GOOGLE_CLOUD_PROJECT", func(t *testing.T) {
		os.Setenv("GOOGLE_CLOUD_PROJECT", "my-project")
		defer os.Unsetenv("GOOGLE_CLOUD_PROJECT")

		assert.True(t, isGCP())
	})

	t.Run("detects from GCP_PROJECT", func(t *testing.T) {
		os.Setenv("GCP_PROJECT", "my-project")
		defer os.Unsetenv("GCP_PROJECT")

		assert.True(t, isGCP())
	})

	t.Run("no GCP without env vars", func(t *testing.T) {
		os.Unsetenv("GOOGLE_CLOUD_PROJECT")
		os.Unsetenv("GCP_PROJECT")

		// Result depends on whether metadata service is reachable
		// Just ensure it doesn't panic
		_ = isGCP()
	})
}

func TestIsAzure(t *testing.T) {
	t.Run("detects from AZURE_SUBSCRIPTION_ID", func(t *testing.T) {
		os.Setenv("AZURE_SUBSCRIPTION_ID", "sub-123")
		defer os.Unsetenv("AZURE_SUBSCRIPTION_ID")

		assert.True(t, isAzure())
	})

	t.Run("detects from WEBSITE_RESOURCE_GROUP", func(t *testing.T) {
		os.Setenv("WEBSITE_RESOURCE_GROUP", "my-group")
		defer os.Unsetenv("WEBSITE_RESOURCE_GROUP")

		assert.True(t, isAzure())
	})

	t.Run("no Azure without env vars", func(t *testing.T) {
		os.Unsetenv("AZURE_SUBSCRIPTION_ID")
		os.Unsetenv("WEBSITE_RESOURCE_GROUP")

		// Result depends on whether metadata service is reachable
		// Just ensure it doesn't panic
		_ = isAzure()
	})
}

func TestDetectAWS(t *testing.T) {
	ctx := context.Background()

	t.Run("returns error when not on AWS", func(t *testing.T) {
		os.Unsetenv("AWS_REGION")
		os.Unsetenv("AWS_DEFAULT_REGION")

		// This will fail because we're not on AWS
		_, err := detectAWS(ctx)
		assert.Error(t, err)
	})
}

func TestDetectGCP(t *testing.T) {
	ctx := context.Background()

	t.Run("returns error when not on GCP", func(t *testing.T) {
		os.Unsetenv("GOOGLE_CLOUD_PROJECT")
		os.Unsetenv("GCP_PROJECT")

		// This will fail because we're not on GCP
		_, err := detectGCP(ctx)
		assert.Error(t, err)
	})
}

func TestDetectAzure(t *testing.T) {
	ctx := context.Background()

	t.Run("returns error when not on Azure", func(t *testing.T) {
		os.Unsetenv("AZURE_SUBSCRIPTION_ID")
		os.Unsetenv("WEBSITE_RESOURCE_GROUP")

		// This will fail because we're not on Azure
		_, err := detectAzure(ctx)
		assert.Error(t, err)
	})
}

func TestCloudProviderDetector(t *testing.T) {
	ctx := context.Background()

	t.Run("returns error for unknown provider", func(t *testing.T) {
		detector := NewCloudProviderDetector("unknown")
		_, err := detector.Detect(ctx)
		assert.Error(t, err)
		assert.Contains(t, err.Error(), "unknown cloud provider")
	})

	t.Run("returns error when not on cloud", func(t *testing.T) {
		// Remove all cloud env vars
		os.Unsetenv("AWS_REGION")
		os.Unsetenv("AWS_DEFAULT_REGION")
		os.Unsetenv("GOOGLE_CLOUD_PROJECT")
		os.Unsetenv("GCP_PROJECT")
		os.Unsetenv("AZURE_SUBSCRIPTION_ID")
		os.Unsetenv("WEBSITE_RESOURCE_GROUP")

		detector := NewCloudProviderDetector("aws")
		_, err := detector.Detect(ctx)
		assert.Error(t, err)
	})
}

func TestWithCloudProvider(t *testing.T) {
	t.Run("adds AWS detector", func(t *testing.T) {
		cfg := &Config{Detectors: []Detector{}}
		opt := WithCloudProvider("aws")
		opt(cfg)

		hasCloud := false
		for _, d := range cfg.Detectors {
			if d.DetectorType() == "cloud" {
				hasCloud = true
				break
			}
		}
		assert.True(t, hasCloud)
	})

	t.Run("adds GCP detector", func(t *testing.T) {
		cfg := &Config{Detectors: []Detector{}}
		opt := WithCloudProvider("gcp")
		opt(cfg)

		hasCloud := false
		for _, d := range cfg.Detectors {
			if d.DetectorType() == "cloud" {
				hasCloud = true
				break
			}
		}
		assert.True(t, hasCloud)
	})

	t.Run("adds Azure detector", func(t *testing.T) {
		cfg := &Config{Detectors: []Detector{}}
		opt := WithCloudProvider("azure")
		opt(cfg)

		hasCloud := false
		for _, d := range cfg.Detectors {
			if d.DetectorType() == "cloud" {
				hasCloud = true
				break
			}
		}
		assert.True(t, hasCloud)
	})

	t.Run("auto-detects cloud provider", func(t *testing.T) {
		// Set GCP env var to simulate GCP environment
		os.Setenv("GOOGLE_CLOUD_PROJECT", "my-project")
		defer os.Unsetenv("GOOGLE_CLOUD_PROJECT")

		cfg := &Config{Detectors: []Detector{}}
		opt := WithCloudProvider("auto")
		opt(cfg)

		hasCloud := false
		for _, d := range cfg.Detectors {
			if d.DetectorType() == "cloud" {
				hasCloud = true
				break
			}
		}
		assert.True(t, hasCloud)
	})
}

func TestGetAzureMetadata(t *testing.T) {
	ctx := context.Background()

	// This test requires Azure metadata service to be available
	// Skip if not available
	if !isAzure() {
		t.Skip("Not running on Azure")
	}

	metadata, err := getAzureMetadata(ctx)
	require.NoError(t, err)
	require.NotNil(t, metadata)

	// Should have compute section
	_, ok := metadata["compute"]
	assert.True(t, ok)
}
